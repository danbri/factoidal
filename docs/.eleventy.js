module.exports = function(eleventyConfig) {
  return {
    dir: {
      input: ".",
      output: "_site",
      includes: "_includes",
      data: "_data"
    },
    markdownTemplateEngine: "njk",
    htmlTemplateEngine: false,
    pathPrefix: "/factoidal/"
  };
};
